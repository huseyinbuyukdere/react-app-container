import React, { useState, useEffect, useRef } from 'react'
import styles from './headerMenuExpandableItem.module.css'
import cn from 'classnames'
import { MenuItem as MenuItemContract } from '../../models'
import HeaderMenuItem from '../HeaderMenuItem'
import OutsideAlerter from '../../hooks/outsideAlerter'

interface HeaderMenuExpandableItemProps {
    label?: string
    onClick?: (routeKey?: string) => void
    iconComp?: any
    iconName?: string
    iconCompStyle?: React.CSSProperties
    subMenuItemList: MenuItemContract[]
    style?: React.CSSProperties
}

const HeaderMenuExpandableItem = (props: HeaderMenuExpandableItemProps) => {
    const [isExpanded, setIsExpanded] = useState(false)
    const refListContainer = useRef<HTMLDivElement>(null)
    var subMenuItemList = props.subMenuItemList.filter(
        (item) => item.label && item.label !== ''
    )
    var maxListHeight = isExpanded
        ? `calc(5rem*${props.subMenuItemList.length})`
        : '0px'


    useEffect(() => {
        setDropdownPosition()
    }, [])

    const setDropdownPosition = () => {
        if (
            refListContainer &&
            refListContainer.current &&
            refListContainer.current.parentElement
        ) {
            var listContainerWidth = refListContainer.current.offsetWidth
            var parentContainerWidth =
                refListContainer.current.parentElement?.offsetWidth
            var translateWidth = listContainerWidth - parentContainerWidth
            translateWidth -=5;
            refListContainer.current.style.transform =
                'translateX(-' + translateWidth + 'px)'
        }
    }

    const onClickOutSide = () => {
        setIsExpanded(false);
    }

    return (
        <OutsideAlerter onClickOutside={onClickOutSide}>
            <div className={styles.menuToggleContainer}>
                <HeaderMenuItem
                    label={props.label ? props.label : ''}
                    iconComp={props.iconComp}
                    iconName={props.iconName}
                    onClick={() => {
                        setIsExpanded(!isExpanded)
                    }}
                />
            </div>
            <div
                ref={refListContainer}
                tabIndex={0}
                onBlur={() => {
                    setIsExpanded(false)
                }}
                className={cn(styles.listContainer, isExpanded && styles.expanded)}
                style={{maxHeight : maxListHeight}}
            >
                {subMenuItemList.map((item) => {
                    return (
                        <div className={styles.menuItemContainer}>
                            <HeaderMenuItem                               
                                iconComp={item.iconComp}
                                iconName={item.iconName}
                                label={item.label ? item.label : ''}
                                onClick={() => {
                                    if (item.onClick) item.onClick()
                                }}
                            />
                        </div>
                    )
                })}
            </div>
        </OutsideAlerter>
    )
}

export default HeaderMenuExpandableItem
