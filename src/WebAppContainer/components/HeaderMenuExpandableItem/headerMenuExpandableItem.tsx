import React, { useState } from 'react'
import styles from './headerMenuExpandableItem.module.css'
import cn from 'classnames'
import { MenuItem as MenuItemContract } from '../../models'
import HeaderMenuItem from '../HeaderMenuItem'

interface HeaderMenuExpandableItemProps {
    label?: string
    onClick?: (routeKey?: string) => void
    iconComp?: any
    iconName?: string
    iconCompStyle? : React.CSSProperties;   
    subMenuItemList : MenuItemContract[];    
    style?: React.CSSProperties
}

const HeaderMenuExpandableItem = (props: HeaderMenuExpandableItemProps) => {

    const [isExpanded, setIsExpanded] = useState(false)

    var subMenuItemList = props.subMenuItemList.filter((item) => item.label && item.label!=='');
    var maxListHeight = isExpanded
        ? `calc(4rem*${props.subMenuItemList.length})`
        : '0px'        
    return (
        <div>
            <div className={styles.menuToggleContainer}>
                <HeaderMenuItem
                    label={props.label ? props.label :''}
                    iconComp={props.iconComp}
                    iconName={props.iconName}
                    onClick={() => {
                        setIsExpanded(!isExpanded)
                    }}
                />
            </div>
            <div
                tabIndex={0}
                onBlur={() => {setIsExpanded(false); console.log("tebrik")}}
                className={cn(styles.listContainer)}
                style={{ maxHeight: maxListHeight }}
            >
                {subMenuItemList.map((item) => {
                    return (
                        <div className={styles.menuItemContainer}>
                            <HeaderMenuItem
                                style={{ padding: '15px' }}
                                iconComp={item.iconComp}
                                iconName={item.iconName}
                                label={item.label ? item.label : ''}                                
                                onClick={() => {
                                    if(item.onClick)
                                        item.onClick();                                    
                                }}                                
                            />
                        </div>
                    )
                })}
            </div>
        </div>
    )
}

export default HeaderMenuExpandableItem;
