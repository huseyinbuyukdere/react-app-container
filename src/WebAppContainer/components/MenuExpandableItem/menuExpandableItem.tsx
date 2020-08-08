import React, { useState, useEffect } from 'react'
import styles from './menuExpandableItem.module.css'
import cn from 'classnames'
import { MenuItem as MenuItemContract } from '../../models'
import MenuItem from '../MenuItem'
import IconComponent from '../../icons'

interface MenuExpandableItemProps {
    label: string
    onClick: (routeKey?: string) => void
    iconComp?: any
    iconName?: string
    selectedRouteKey: string
    subMenuItemList: MenuItemContract[]
}

const MenuExpandableItem = (props: MenuExpandableItemProps) => {
    const isAnySelectedSubRoute = props.subMenuItemList.some(
        (item) => props.selectedRouteKey ? item.routeKey === props.selectedRouteKey : false
    )
    const [isExpanded, setIsExpanded] = useState(isAnySelectedSubRoute)

    useEffect(() => {

        var isAnySelectedSubRoute = props.subMenuItemList.some(
            (item) => props.selectedRouteKey ? item.routeKey === props.selectedRouteKey : false
        )
        if(!isExpanded)
        {
            setIsExpanded(isAnySelectedSubRoute);
        }      
    // eslint-disable-next-line react-hooks/exhaustive-deps  
    }, [props.selectedRouteKey])

    var maxListHeight = isExpanded
        ? `calc(4rem*${props.subMenuItemList.length})`
        : '0px'
    return (
        <div>
            <div className={styles.menuToggleContainer}>
                <MenuItem
                    label={props.label}
                    iconComp={props.iconComp}
                    iconName={props.iconName}
                    rightIconName={isExpanded ? 'expand_less' : 'expand_more'}
                    rightIconCompStyle={{ height: '18px', width: '18px' }}
                    onClick={() => {
                        setIsExpanded(!isExpanded)
                    }}
                    isSelected={false}
                />
            </div>
            <div
                className={cn(styles.listContainer)}
                style={{ maxHeight: maxListHeight }}
            >
                {props.subMenuItemList.map((item) => {
                    var isSelected = props.selectedRouteKey ? item.routeKey === props.selectedRouteKey : false
                    var checkBoxIcon = (
                        <div
                            className={cn(
                                styles.subItemIconContainer,
                                isSelected && styles.selected
                            )}
                        >
                            <IconComponent
                                name="radio_button_checked"
                                height={8}
                                width={8}
                            />
                        </div>
                    )
                    return (
                        <div className={styles.menuItemContainer}>
                            <MenuItem
                                style={{ paddingLeft: '40px' }}
                                label={item.label ? item.label : ''}
                                iconComp={checkBoxIcon}
                                onClick={() => {
                                    if(item.onClick)
                                        item.onClick();
                                }}
                                isSelected={isSelected}
                            />
                        </div>
                    )
                })}
            </div>
        </div>
    )
}

export default MenuExpandableItem
